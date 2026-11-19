/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat (git blob 344d1ff74929b382451c35b94a4bbd19aeeeaa57, sha256 9f2cd188bf4d0eebfcc2683e14d66785b5ea69c8beba60147a025e955ab64f05).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel

private theorem hc : (1/2 : ℝ) ≤ Real.sqrt 3 / 2 := by
  rw [div_le_div_iff_of_pos_right two_pos]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

private theorem hu : (1/2 : ℝ) ≤ 1 := by norm_num
private theorem hd₂ : (0 : ℝ) < 2 := by norm_num
private theorem hd : (1/2 : ℝ) ≤ 2 := by norm_num

theorem solution :
    CoversModCentre ℚ (productionPinsGeneral ℚ).D := by
  rw [productionPinsGeneral_D]
  exact CoversModCentre.mono (centreCutSiegelSet_subset_classRepSiegelSet ℚ (1/2) 1 (1/2) 2)
    (centreCutSiegelSet_coversModCentre_rat hc hu hd₂ hd)
