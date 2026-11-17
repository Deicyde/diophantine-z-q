/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one (git blob b70be681ed3c711566c577e2493acfc2a355363c, sha256 b8580ed888ab1c57bf05827352d772da7a0fa4485255446d85badd66087bc8fa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
    (p q c : ℝ) (hpc : 0 < p + c) (hcq : c < q) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioi 0) := by
  revert p q c hpc hcq
  exact @_root_.P2MW.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one.solution
