/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1 (git blob d7fd87e6d8f377c8bf3de556056ce7837ecfe320, sha256 defbe7437e126fc7669cf1c7524a7d1767f39dd18d8496094510783b77617f92).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) := by
  revert K M hM ζ hζ
  exact @_root_.P2MW.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1.solution
